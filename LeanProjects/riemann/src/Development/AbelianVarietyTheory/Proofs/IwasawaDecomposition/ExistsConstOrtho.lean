import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevelTranslateJetNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow

namespace GlobalTheory.OneMapRef.Kappa

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.AdTh.GenConst
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ex_eq [Algebra c.F ℂ] {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (A A' : AnFib X bas idx e x L y) :
    A.ex = A'.ex :=
  GlobalTheory.CuspFamilyCompare.exp_unique A.ex_add A'.ex_add A.hol A'.hol (fun j => y.u (e j).1 (e j).2)
    (fun j => by simpa only [Equiv.symm_apply_apply] using A.der (e j))
    (fun j => by simpa only [Equiv.symm_apply_apply] using A'.der (e j))

theorem exists_root {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l L mk) {n N : ℕ}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (hY : IsRoots l L mk N Y) {y : Matrix (Fin n) (Fin r) E}
    (hy : ∀ b, (l.M : E) • y b ∈ Mfr l • L) : ∃ q, ∀ b, Y q b - y b ∈ L := by
  have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (LevCover.M_pos l).ne'
  choose a ha t ht h using fun b => hmk.surj _ (hy b)
  refine ⟨fun b => Submodule.Quotient.mk (a b), fun b => ?_⟩
  obtain ⟨⟨a', ha', hq, h'⟩, -⟩ := hY (fun b => Submodule.Quotient.mk (a b)) b
  obtain ⟨d, hd⟩ := LevCover.modN_of_mem_both l ((Submodule.Quotient.eq _).1 hq) (Submodule.sub_mem _ ha' (ha b))
  have e₀ : mk a' = mk (a b) + (l.M : E) • mk d := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hd, ← map_add, add_sub_cancel]
  have e₁ : y b = (l.M : E)⁻¹ • mk (a b) + t b := by
    rw [← inv_smul_smul₀ hM0 (y b), h, smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
  rw [e₀, smul_add, inv_smul_smul₀ hM0] at h'
  convert L.sub_mem (L.add_mem h' (hmk.mem d)) (ht b) using 1
  rw [e₁]
  abel

theorem exists_const {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (hr1 : 1 ≤ r) (k : U.Comp) (t : ℝ) (ht : ∀ τ, (U.X k).c τ = t) (n : ℕ) (hn : Even n)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas)
    (hI : ∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (e j).1) (e j).2)
    (v : TF n g) (hv : IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v) :
    ∃ C : ℂ, ∀ x : (U.X k).dom, (U.X k).IsOrtho x.1 → letI : Algebra c.F ℂ := σ.toAlgebra
      ∀ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC U k x)) (ϑ : (Fin g → ℂ) → ℂ), A.Reads 1 (unC U k x).s ϑ →
        ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hC := GlobalTheory.ChartFree.chartIndep
  obtain ⟨W⟩ := nonempty_uw hU
  obtain rfl : g = W.g := Fin.equiv_iff_eq.1 ⟨e.trans W.e.symm⟩
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, hDe, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  subst hDe
  obtain rfl : idx = Dc.idx := idx_unique hs fun x u j => (hI x u j).trans (Dc.per_eq x u j).symm
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv
  have hpt : ∀ x (hx : x ∈ (U.X k).dom), IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib (U.X k) bas Dc.idx Dc.e x (U.X k).Λ (unC U k ⟨x, hx⟩)) (ϑ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC U k ⟨x, hx⟩).s ϑ ∧
        IsTheta1 (U.X k) bas Dc.idx (H.w0 : E) x (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas Dc.idx x (U.X k).Λ ϑ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ (z b) = κ * thA (U.X k) bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨π, hπ⟩ : ∃ π : Fin W.g ≃ Fin W.g, π.trans W.e = Dc.e := ⟨Dc.e.trans W.e.symm, by ext1; simp⟩
    have hπ' : ∀ j, W.e j = Dc.e (π.symm j) := fun j => by rw [← hπ]; simp
    have hid : π.trans (π.symm.trans Dc.idx) = Dc.idx := by ext1; simp
    obtain ⟨A₀, hA₀, ϑ₀, hϑ₀, hm₀⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k bas (π.symm.trans Dc.idx) hs
      (fun x u j => by rw [hπ']; exact Dc.per_eq x u _) (fun j => by rw [hπ']; exact Dc.ty_eq _) ⟨x, hx⟩ hux
    have h1 := exists_anFib_trans π A₀
    have hmean := meanOne_trans π hm₀
    rw [hid, hπ] at h1
    rw [hid] at hmean
    obtain ⟨A, hA, hR⟩ := h1
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x _ _ A hs hx hL _ (hR _ hϑ₀)
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x hx _ hT
    exact ⟨κ, hnorm x hx hux _ κ hT hmean hκ, A, _, hA _ hA₀, hR _ hϑ₀, hT, hmean, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const (U.X k) (Formalism.L2.PjFree.laU U 0 n k) ρ hρ κ hκ
  refine ⟨C, fun x hox A ϑ hϑ => ?_⟩
  have hux : IsUnitFr (U.X k) x.1 := PullbackSections.PfSupAtUnit.dmin_ortho _ hox
  obtain ⟨A₀, ϑ₀, hA₀, -, hT₀, hmean, hprod₀⟩ := hpt x.1 x.2 hux
  have hA : A.Marked (W.mark k) := fun a ha => (hA₀ a ha).trans (congrFun (ex_eq A₀ A) _)
  obtain ⟨κ', hprod⟩ := VacProd.prod_eq_mul_thA E r _ _ bas Dc.idx n hs hn _ hw hw' _ hL v hv x.1 x.2 _
    (isTheta1_of_reads_generator E H Dw l Xo c r _ _ bas Dc.idx Dc.e x.1 _ _ A hs x.2 hL _ hϑ)
  have hM := LevCover.M_pos l
  obtain ⟨-, -, h1, h2, hY⟩ := DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')
  obtain ⟨Y, hY⟩ := hY n l.M hM
  have ht0 : 0 < t := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
    rw [← ht ⟨τ, hτ⟩]
    exact mul_pos two_pos (norm_pos_iff.2 ((_root_.map_ne_zero τ).2 (U.X k).ξ0_ne))
  obtain ⟨y, hy, hne⟩ := exists_level_translate_jet_ne_zero E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn H.w0 hw' _ hL
    x.1 x.2 hox t ht0 ht (Mfr l) l.M l.odd (by rw [h1, h2]) v hv ϑ₀ _ hT₀ hmean hprod₀ 1 one_ne_zero
    (by rw [MvPolynomial.totalDegree_one]; exact le_trans (by norm_num) l.three_le)
  obtain ⟨q, hq⟩ := exists_root hmk hY hy
  have h3 := right_ne_zero_of_mul (hne _ hq)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  have hsec : f ∈ sec Xo c 0 n := GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩
  have hsb : IsSB (heisG (U.X k) bas (Y q) v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g bas Dc.idx n hs hn).2.2.2 (Y q) v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr bas Dc.idx n hs hn Dc.k Dc.k'
    _ hsb _ (Dc.mem 1 hP.1)
  have hS := hU.2.2.2.2.1 0 n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = Formalism.L2.PjFree.laU U 0 n k := Dc.wt_eq
  rw [hwt] at hhol
  have hval : ∀ x' (hx' : x' ∈ (U.X k).dom)
      (A' : AnFib (U.X k) bas Dc.idx Dc.e x' (U.X k).Λ (unC U k ⟨x', hx'⟩)) (ϑ' : (Fin W.g → ℂ) → ℂ) (κ'' : ℂ),
      A'.Marked (W.mark k) → A'.Reads 1 (unC U k ⟨x', hx'⟩).s ϑ' →
      (∀ z : Fin n → Fin W.g → ℂ, ∏ b, ϑ' (z b) = κ'' * thA (U.X k) bas Dc.idx v x' z) →
      Formalism.L2.PjFree.rdU U f k x' = κ'' * thP (U.X k) Dc.hr bas Dc.idx (heisG (U.X k) bas (Y q) v)
        (MvPolynomial.rename Dc.eL (MvPolynomial.map σ 1)) x' := fun x' hx' A' ϑ' κ'' hA' hϑ' hprod' => by
    have := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) bas Dc.idx Dc.e x' _ _ A' hs hx' hL Dw.p n Dc.hr
      Dc.eL hU.1 hn Dc.dir_eq nab hnab ϑ' v _ hϑ' hv hprod' (W.mark k) hmk hA' (fun b => levRep (q b)) (Y q)
      (fun b => by
        obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
        exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
          (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
      (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k ⟨x', hx'⟩))
    exact Eq.trans (dif_pos hx') this
  have h4 := hCe _ _ hS.1 hhol.1 (fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩)
    (fun x' hx' hu' => by
      obtain ⟨A', ϑ', hA', hϑ', -, -, hprod'⟩ := hpt x' hx' hu'
      exact hval x' hx' A' ϑ' _ hA' hϑ' hprod') x.1 x.2
  rw [hval x.1 x.2 A ϑ κ' hA hϑ hprod, map_one, map_one] at h4
  rw [← mul_right_cancel₀ h3 h4]
  exact hprod

end GlobalTheory.OneMapRef.Kappa

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.exists_const_ortho : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (t : ℝ), (∀ τ, (U.X k).c τ = t) → ∀ n : ℕ, Even n → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → Matched c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : D.host.E) (tens (stdL D.host.E n) (U.X k).Λ) v → ∃ C : ℂ, ∀ x : (U.X k).dom, (U.X k).IsOrtho x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (ptC U k x)) (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U k x).s th → ∀ z : Fin n → Fin g → ℂ, ∏ b, th (z b) = C * thA (U.X k) bas idx v x.1 z := by
  intro D H Dw l Xo c σ r U hσ hU hr _ k t ht n hn g bas idx e hs hm v hv
  exact GlobalTheory.OneMapRef.Kappa.exists_const (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr k t ht n hn bas idx e hs hm.1 v hv
