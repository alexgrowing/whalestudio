import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValues
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.JSpanPf

private theorem span_of_bc {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
    {S : Formalism.L2.Col.GSD K} {S' : Formalism.L2.Col.GSD L} (b : Formalism.L2.Col.GSDBC ι S S') {M M' : Type} [AddCommGroup M'] [Module L M']
    (r : S.EqFun → M) (r' : S'.EqFun ≃ₗ[L] M') (c : L →+* ℂ) {α α' U U' : Type} (n : NormedAddCommGroup U)
    (n' : NormedAddCommGroup U') (ip : InnerProductSpace ℂ U) (ip' : InnerProductSpace ℂ U') (hα : α' = α) (hU : U' = U)
    (hn : HEq n' n) (hip : HEq ip' ip) (j : M → α → U) (j' : M' →ₛₗ[c] (α' → U'))
    (h : ∀ φ, HEq (j' (r' (b.lift φ))) (j (r φ))) (x' : M') :
    ∃ (m : ℕ) (a : Fin m → L) (x : Fin m → M), HEq (j' x') (∑ k, c (a k) • j (x k)) := by
  subst hα hU
  cases hn
  cases hip
  obtain ⟨F⟩ := Formalism.L2.Col.CoefFrame.nonempty ι
  obtain ⟨φ', rfl⟩ := r'.surjective x'
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 (b.mem_span_lift F φ')
  choose ψ hψ using fun k => (g k).2
  refine ⟨m, a, fun k => r (ψ k), heq_of_eq ?_⟩
  rw [← hg, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, LinearMap.map_smulₛₗ, ← hψ k, eq_of_heq (h (ψ k))]

set_option maxHeartbeats 4000000 in

private theorem exists_bc {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl) (hE : Enl0 B B') (hf : HEq f' f) (hpx : HEq w'.px w.px)
    (k k' : ℕ) (hk : k' = k) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) :
    ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k)
      (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 k'),
      ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k).EqFun) d d', HEq d' d →
        HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((b.lift ψ).1 d').1)
          (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hk
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hv : (Base.primes (baseOfColW w') w'.px).vGs = (Base.primes (baseOfColW w) w.px).vGs := by
    rw [hpx']
    rfl
  have hφ' : ∀ x, (baseOfColW w').embLL (φ x) = (baseOfColW w).embLL x := hφ
  have hC : w'.I.C = w.I.C := w'.C_eq.trans ((eq_of_heq hf).trans w.C_eq.symm)
  refine GlobalTheory.Mem.R3.DefLatBC.gsdbc_round_reidx (baseOfColW w).fields φ (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hφ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hφ' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' _).trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w Wt).symm)
  · refine glue_inv_coefMap_of_empty φ (twistRamifiedPrimes_empty_colTuples w Wt) (twistRamifiedPrimes_empty_colTuples w' _) _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of φ p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hφ']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    rw [hC] at e1
    exact e1.trans e2.symm

set_option maxHeartbeats 2000000 in

private theorem gf_eq {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m)
    (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    (↥(Bridge.Gf (Vc (w'.st Z').toD7 i')) : Type) = ↥(Bridge.Gf (Vc (w.st Z).toD7 i)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at h
  subst h
  have e0 : i = i' := Fin.ext hi
  subst e0
  rfl

end GlobalTheory.Mem.R3.Rw.JSpanPf

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → RSideW z Wt' R' → JSpan z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hRS i i' hii x'
  obt ⟨ι, hι⟩ := exists_iota_comp B.embLL B'.embLL hE.2.2.2
  obt ⟨b, hb⟩ := GlobalTheory.Mem.R3.Rw.JSpanPf.exists_bc w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) ι hι
  have hj := fun φ => hRS.2.2.2.2.2.2.2.2.2.2.2.2.2 i i' hii (Formalism.L2.Col.mtKOk _ _ _ _ hX _) (Formalism.L2.Col.mtKOk _ _ _ _ hX' _) φ
    (b.lift φ) (hb φ)
  have hc := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have key := GlobalTheory.Mem.R3.Rw.JSpanPf.span_of_bc b
    (fun φ => (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX _) φ)
    ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX' _))
    B'.embLL (z.R.cV i).nW (R'.cV i').nW (z.R.cV i).iW (R'.cV i').iW (GlobalTheory.Mem.R3.Rw.JSpanPf.gf_eq Z Z' hE.1 i i' hii)
    (eq_of_heq hc.1) hc.2.2.1 hc.2.2.2.1
    (fun x => z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :))))
    ((by with_unfolding_all exact (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) :))) ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (x' :)))
  exact (by with_unfolding_all exact (key :))
