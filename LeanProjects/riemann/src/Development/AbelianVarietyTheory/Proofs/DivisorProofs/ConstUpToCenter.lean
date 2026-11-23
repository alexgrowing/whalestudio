import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OneMapAll

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.OnCmp.const_upTo_center : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, GlobalTheory.AdTh.SerOf (O i) (κ i) (v₀ i (sg0 D A)) (u • cc) 1 → ∃ z ∈ Subgroup.center G, ∃ (ζ : D.what₂.LL) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧ ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g, (O i).phi (u • cc) f g = D.what₂.embLL ζ * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins hU hIo h0 hPh hSpan cc hcc u hser
  have hP := hpins.2
  obtain ⟨hE, ⟨hLL, -, -, hcU, -, z, hz, hrowT⟩, -⟩ := hPh h0
  obtain ⟨ζ, hζL, ⟨m, hm, hζm⟩, hT1⟩ := hrowT ()
  obtain ⟨ζ', rfl⟩ := (AlgHom.mem_fieldRange).1 hζL
  have hζ : D.what₂.embLL.toRatAlgHom ζ' = D.what₂.embLL ζ' := rfl
  rw [hζ] at hζm hT1
  clear hζL
  have hs0 : ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (lieFac_pos _ _ _).ne'
  have gen : ∀ x, (O i).Plc () x → ∀ Fr ∈ sec (T.J.Q.Xo ((i : ℕ) + 1)) (O i).c' (wtA (κ i)) (Vc D i).rank,
      IsSum (O i) () x Fr → ∀ q,
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro x hx Fr hF hsum q
    have h1 := (hT1 x hx).2 Fr hF hsum q
    obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple ()).reps
    obtain ⟨y, hy⟩ := (hPl x).1 hx
    have h2 := hser.2.2 () h J' hR _ x hy Fr hF hsum q.out
    have h3 : actLev (O i).c' (O i).lev2 1 Fr = Fr := actL_one _ _ _ hP.act.2.total hP.act.2.func hP.act.2.one hF.1
    rw [hA _ x hy] at h1
    unfold geo
    rw [h3]
    simp only [jFn, onQ, adel, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul, one_mul] at h1 h2 ⊢
    linear_combination h1 - h2
  have span : ∀ q, ∀ Fr ∈ cuspOver (O i) (κ i),
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro q Fr hF
    have hF' := hSpan hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨hgc, x, hx, hgx⟩ := hg
      exact gen x hx g ((mem_cusp _ _ _ _ _ _).1 hgc).1 hgx q
    | zero =>
      have e := geo_smul (O i) (u • cc) 1 0 0 q
      have e' := geo_smul (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z 0 0 q
      rw [zero_smul] at e e'
      rw [e, e']
      simp
    | add f g _ _ hf hg => rw [geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf => rw [geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have rep : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ q : AutQ (Wc D i),
      (O i).phi (u • cc) f q.out =
        D.what₂.embLL ζ' * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) q.out := by
    intro f hf q
    rw [hn] at hf
    have hfs : f ∈ sec _ _ (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hf).1
    have hF := ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ (O i).hle _ (T.J.U ((i : ℕ) + 1)) _ _ _ hfs).2).2 hf
    have hBC := GlobalTheory.FieldBCModel.isBC_rulBC (O i).hle hfs.1
    have hs1 : ∀ k, ![f] k ∈ sec _ T.J.Q.c (wtA (κ i)) (Vc D i).rank := fun k => by
      rw [Subsingleton.elim k 0]; exact hfs
    have e := span q _ hF
    rw [geo_of_isBC (O i) hP.act.1 _ 1 (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q,
      geo_of_isBC (O i) hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q] at e
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
    have h1 : actLev T.J.toCore.Q.c (O i).lev2 1 f = f :=
      actL_one _ _ _ hP.act.1.total hP.act.1.func hP.act.1.one hfs.1
    rw [h1] at e
    exact mul_left_cancel₀ hs0 (e.trans (by ring))
  have hcomp : ∀ γ ∈ GQ (Wc D i), ∀ g, ((O i).dict (γ * g)).1 = ((O i).dict g).1 := by
    obtain ⟨th, hr, -, hd⟩ := hT.j.dictU ((i : ℕ) + 1) (inR i) _ T.J.good_σ₀
    have key : ∀ (W : HSp D) (hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = W), ∀ γ ∈ GQ W, ∀ g,
        (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) (γ * g)).1 = (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) g).1 := by
      rintro W rfl γ hγ g
      obtain ⟨γ', -, he⟩ := hd.1 γ hγ g
      have e := congrArg Sigma.fst he
      exact e
    exact key _ (O i).hV
  have hsplit : ∀ (c' : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (f : T.J.R ((i : ℕ) + 1)) g,
      (O i).phi c' f g = c' ((O i).dict g).1 * (O i).phi (fun _ => 1) f g := by
    intro c' f g
    show c' _ * _ * _ = c' _ * (1 * _ * _)
    ring
  have hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = Wc D i := (O i).hV
  have hinv : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f (γ * g) = (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f g :=
    fun f hf => GlobalTheory.OneMapTuples.psi_inv T.J _ hV hT.j (inR i) (dom_wtA (κ i)) hf
  refine ⟨z, hz, ζ', m, hm, ?_, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, map_one]
    exact hζm
  intro f hf g
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  have hzf := (hE z k hk f hf).1
  have hq : g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ ∈ GQ (Wc D i) :=
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel (GQ (Wc D i))) g)
  set γ := g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ with hγ
  have hg : g = γ * (⟦g⟧ : AutQ (Wc D i)).out := by rw [hγ, inv_mul_cancel_right]
  have hL : (O i).phi (u • cc) f g = (O i).phi (u • cc) f (⟦g⟧ : AutQ (Wc D i)).out := by
    have e := hinv f hf γ hq (⟦g⟧ : AutQ (Wc D i)).out
    rw [← hg] at e
    rw [hsplit (T.J.cE _ _) f g, hsplit (T.J.cE _ _) f, hg, hcomp γ hq] at e
    rw [← hg] at e
    have hne : T.J.cE ((i : ℕ) + 1) (O i).s0 ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 ≠ 0 :=
      norm_ne_zero_iff.1 ((hcU _).trans_ne one_ne_zero)
    have hc : ((O i).dict g).1 = ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 := by
      have := hcomp γ hq (⟦g⟧ : AutQ (Wc D i)).out
      rwa [← hg] at this
    rw [hsplit (u • cc) f g, hsplit (u • cc) f, hc, mul_left_cancel₀ hne e]
  rw [hL, rep f hf, ← hinv _ hzf γ hq, ← hg]
