import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.OffTwist

theorem entry_mem_of_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E))
    (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ s, (Pi.single s (T : E) : Fin n → E) ∈ L)
    {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ Formalism.UG.levelVL σ J v L) (r s : Fin n) :
    g.val r s ∈ intV E v := by
  replace hg : g ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L) := hg.2
  have hle : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L, ∀ j, y j ∈ intV E v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      intro j
      obtain ⟨c, hc⟩ := h1 x hx j
      refine Subring.subset_closure (Or.inl ⟨⟨x j, c, hc.symm⟩, rfl⟩)
    | zero => intro j; exact zero_mem _
    | add x y _ _ hx hy => intro j; exact add_mem (hx j) (hy j)
    | smul c x _ hx => intro j; exact mul_mem c.2 (hx j)
  have hv : Valued.v ((T : ℕ) : v.adicCompletion F) = 1 := by
    have e : ((T : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (T : 𝓞 F)) := by
      simp
    rw [e]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hT
  have hne : ((T : ℕ) : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  have hinv : ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hc : (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨_, hinv⟩, rfl⟩)
  have hmem : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) ∈
      Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L := Submodule.subset_span ⟨_, h2 s, rfl⟩
  have h3 := hle _ ((hg _).1 hmem) r
  have e3 : (g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) r =
      g.val r s * (T : ℕ) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [e3] at h3
  have e4 : ((T : ℕ) : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹) = 1 := by
    have : ((T : ℕ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F) :=
      (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)) T).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
    rfl
  have h4 := mul_mem h3 hc
  rwa [mul_assoc, e4, mul_one] at h4

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prV_toEAf (v : GlobalTheory.FinPl.Pl D) (x : AE D) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D x) =
      Algebra.TensorProduct.comm D.host.F _ _ (GlobalTheory.FinPl.compAt D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero, map_zero]
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, map_add]

theorem pr_eq_zero (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) = 0) : q.pr x = 0 := by
  rw [prV_toEAf, map_eq_zero_iff _ (AlgEquiv.injective _)] at hx
  have h1 : GlobalTheory.FinPlLoc.idem D (· = q.v) * x = 0 := by
    rw [← GlobalTheory.FinPlLoc.mem_idOff_iff]
    refine (Submodule.mem_iInf _).2 ?_
    rintro ⟨w, rfl⟩
    exact RingHom.mem_ker.2 hx
  have he := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.e_mem_idAt q)
  have h2 : q.sec (q.pr x) = 0 := by
    rw [q.sec_pr, ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _), mul_assoc, h1, mul_zero]
  rw [← q.pr_sec (q.pr x), h2, map_zero]

set_option maxHeartbeats 1600000 in

theorem exists_int_lift (v : GlobalTheory.FinPl.Pl D) (y : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) (hy : y ∈ intV D.host.E v) :
    ∃ x : AE D, finPart D x ∈ intAE D ∧ Formalism.UG.prV (E := D.host.E) v (toEAf D x) = y := by
  have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨c, rfl⟩
    · refine ⟨(1 : AF D.host.F) ⊗ₜ (c : D.host.E), AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩, rfl⟩
    · let α : Af D.host.F := RestrictedProduct.mk (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F)
        (Filter.Eventually.of_forall fun w => by
          by_cases h : w = v
          · subst h; rw [Pi.single_eq_same]; exact c.2
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
      have hα : α ∈ intAf D.host.F := fun w => by
        show (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) w ∈ _
        by_cases h : w = v
        · subst h; rw [Pi.single_eq_same]; exact c.2
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      refine ⟨pairA D.host.F 0 α ⊗ₜ (1 : D.host.E), ?_, ?_⟩
      · rw [GlobalTheory.FinPlLoc.finPart_pair]
        exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩
      · rw [prV_toEAf, GlobalTheory.FinPlLoc.compAt_pair, Algebra.TensorProduct.comm_tmul]
        show (1 : D.host.E) ⊗ₜ[D.host.F] ((Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) v) = _
        rw [Pi.single_eq_same]
  | zero => exact ⟨0, by rw [RingHom.map_zero]; exact zero_mem _, by rw [RingHom.map_zero, RingHom.map_zero]⟩
  | one =>
    refine ⟨1, ?_, by rw [RingHom.map_one, RingHom.map_one]⟩
    rw [RingHom.map_one, Algebra.TensorProduct.one_def]
    exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, by rw [RingHom.map_add]; exact add_mem hx hy, by rw [RingHom.map_add, RingHom.map_add]⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, by rw [RingHom.map_neg]; exact neg_mem hx, by rw [RingHom.map_neg, RingHom.map_neg]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x * y, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hx hy, by rw [RingHom.map_mul, RingHom.map_mul]⟩

theorem pr_mem_int (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) ∈ intV D.host.E q.v) :
    q.pr x ∈ 𝒪[k] := by
  obtain ⟨x', h1, h2⟩ := exists_int_lift q.v _ hx
  have h3 : q.pr (x - x') = 0 := pr_eq_zero q _ (by rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self])
  rw [RingHom.map_sub, sub_eq_zero] at h3
  rw [h3, q.int_iff, q.sec_pr, RingHom.map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ?_ h1
  have := (q.int_iff 1).1 (one_mem _)
  rwa [← map_one q.pr, q.sec_pr, mul_one] at this

theorem conj_int {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (hF : IsStdFr pos F)
    (M : Matrix (Fin N) (Fin N) k) (hM : ∀ r s, M r s ∈ 𝒪[k]) (a b : Y) : (F.γ * M * F.β) a b ∈ 𝒪[k] := by
  obtain ⟨e, -, he⟩ := hF
  have hγ : F.γ = (1 : Matrix (Fin N) (Fin N) k).submatrix e id := by
    have h1 : (1 : Matrix (Fin N) (Fin N) k).submatrix e id * F.β = 1 := by
      rw [he, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one, Matrix.submatrix_one_equiv]
    rw [← Matrix.one_mul F.γ, ← h1, Matrix.mul_assoc, F.βγ, Matrix.mul_one]
  have h : F.γ * M * F.β = M.submatrix e e := by
    rw [hγ, he]
    conv_lhs => rw [← Matrix.submatrix_id_id M]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.one_mul, Matrix.mul_one]
  rw [h]
  exact hM _ _

theorem locHom_mem_KO (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {Y : Type} [Fintype Y] [DecidableEq Y]
    {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k S.rank Y) (hF : IsStdFr pos F) (T : ℕ) (hT : (T : 𝓞 D.host.F) ∉ q.v.asIdeal)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (h2 : ∀ s, (Pi.single s (T : D.host.E) : Fin n → D.host.E) ∈ L) {σ : D.host.E →ₐ[D.host.F] D.host.E}
    {J : Matrix (Fin n) (Fin n) D.host.E} (U : Subgroup (GA D S))
    (hU : ∀ g ∈ U, ∃ κ : GL (Fin n) (EF D), κ.val = finM S hn g ∧ Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ ∈
      Formalism.UG.levelVL σ J q.v L) :
    ∀ g ∈ U, GlobalTheory.LevIdx.locHom q S F g ∈ KO k Y := by
  subst hn
  have key : ∀ g ∈ U, ∀ a b, (GlobalTheory.LevIdx.locHom q S F g).val a b ∈ 𝒪[k] := by
    intro g hg
    obtain ⟨κ, hκ, hs⟩ := hU g hg
    refine conj_int F hF _ fun r s => ?_
    have h := entry_mem_of_stab q.v T hT L h1 h2 _ hs r s
    have e : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ).val r s =
        Formalism.UG.prV (E := D.host.E) q.v (toEAf D (mt S g r s)) := by
      show Formalism.UG.prV (E := D.host.E) q.v (κ.val r s) = _
      rw [hκ]; rfl
    rw [e] at h
    exact pr_mem_int q _ h
  intro g hg
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨key g hg, key _ (inv_mem hg)⟩

end GlobalTheory.LevProd.OffTwist

theorem GlobalTheory.LevProd.phi_mem_KO_of_not_twAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : QJ a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : QJ a t), J.Reads → ∀ i, ¬ GlobalTheory.LevProd.twAt J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), GlobalTheory.LevProd.phi J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ ((ha.stdQ _ _).1 j _) (B.T u) hv
    (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
  · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
    exact ⟨c, hc⟩
  · refine (hlb _).2 fun r => ?_
    by_cases h : r = s
    · subst h
      refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
    · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
  · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
    exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
      ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩

end
